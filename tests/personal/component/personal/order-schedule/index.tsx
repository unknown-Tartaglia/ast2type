/*
 *@Date: 2024-07-30 10:20:11
 *@Description: 个人中心订单进度区域
 */
 import {
  CommonUtils,
  DarkStore,
  PlatformUtils,
  Listener,
  Service as env,
  RouterUtils,
  PAGE_TYPE,
  handleImgUrl,
  fontStore,
  FONT_MUTIPLE,
  TimeUtils,
} from '@hw-vmall/vrn-basic-comp';
import { FastImageView, SwiperDots } from '@hw-vmall/vrn-bussiness-comp';
import React, { PureComponent } from 'react';
import {
  View,
  ScrollView,
  Text,
  Dimensions,
  TouchableOpacity,
  PanResponder,
} from 'react-native';
import Swiper from 'react-native-web-swiper';
import { WebScheduleStyle } from './style/index';
const dsWindow = Dimensions.get('window');

class OrderSchedule extends PureComponent<any, any> {
  scrollView: any;
  isDragging: boolean = false;
  gestureListener = new Listener('orderSchedule');
  timerSchedule: any;
  timerNavigateTo: any;
  imgListWap: any[] = [];
  switch: any;
  scrollTimer: any;
  activeImgColorList: any[] = []; // 每个图片的颜色值
  _gestureHandlers: any;
  constructor(props: any) {
    super(props);
    this.state = {
      currentPage: 1,
    };
  }
  
  componentWillMount() {
    this.startTimer();
    this._gestureHandlers = PanResponder.create({
      // 确定是否在view组在 手指按下 的时候响应touch事件
      onStartShouldSetPanResponder: () => true,
      // 确定是否在view组件手指移动的时候响应touch事件后，是否阻止事件冒泡（它的子组件的事件将不被响应）
      onMoveShouldSetPanResponderCapture: () => true,
    });
  }

  componentDidUpdate() {
    this.startTimer();
  }

  componentWillUnmount() {
    this.scrollTimer && clearTimeout(this.scrollTimer);
    this.timerNavigateTo && clearTimeout(this.timerNavigateTo);
    this.timerSchedule && clearTimeout(this.timerSchedule);
  }

  isWeb = () => {
    const width: number = CommonUtils.getWindowSize(PAGE_TYPE.personal).screenWidth;
    return PlatformUtils.isPc(width);
  };

  refScrollView = (view: any) => {
    this.scrollView = view;
  };
  // 拖拽的时候清空定时器
  scrollBeginDrag = async (e: any) => {
    this.isDragging = true;
    this.gestureListener.triggerEvent('onBegin', { value: e });
    this.stopTimer();
  };
  stopTimer() {
    this.timerSchedule && clearTimeout(this.timerSchedule);
  };
  // 拖拽结束 重启定时器
  scrollEndDrag = (e: any) => {
    this.gestureListener.triggerEvent('onRelease', { value: e });
    this.startTimer();
  };
  // 开启定时器
  startTimer() {
    const { latestOrderLogList, swiperWidth } = this.props
    if (!PlatformUtils.isWap(dsWindow.width) && latestOrderLogList?.length) {
      // 2.添加定时器
      this.stopTimer();
      this.timerSchedule = setTimeout(() => {
        // 2.1设置原点
        let activePage = 0;
        activePage = this.state.currentPage + 1;
        const offsetX = activePage * swiperWidth;
        if (activePage === this.imgListWap.length - 1) {
          this.scrollView?.scrollTo({
            x: this.imgListWap.length * swiperWidth,
            y: 0,
            animated: true,
          });
        } else {
          this.scrollView?.scrollTo({ x: offsetX, y: 0, animated: true });
        }
      }, 7000);
    }
    return true;
  };
  onAnimatinonEnd = (e: any) => {
    this.isDragging = false;
    const scrollOffset = e.nativeEvent.contentOffset.x;
    const activePage = Math.round(scrollOffset / this.props.swiperWidth);
    let stateParam: any = {
      currentPage: activePage,
    };
    stateParam.currentPage = this.fixFirstAndLastPos(activePage);
    this.setState(stateParam);
  };
  // 滑到首尾位置后，矫正图片位置
  fixFirstAndLastPos = (activePage: number) => {
    if (this.scrollView === null) {
      return;
    }
    let currentPage: number = activePage;
    // 根据偏移量计算当前页面的位置
    if (activePage === 0) {
      currentPage = this.imgListWap.length - 2;
      this.scrollView?.scrollTo({
        x: currentPage * this.props.swiperWidth,
        y: 0,
        animated: false,
      });
    }
    if (activePage === this.imgListWap.length - 1) {
      currentPage = 1;
      this.scrollTimer = setTimeout(() => {
        this.scrollView?.scrollTo({
          x: currentPage * this.props.swiperWidth,
          y: 0,
          animated: false,
        });
      }, 100);
    }
    return currentPage;
  };
  onScroll(e: any) {
    if (this.isDragging) {
      return;
    }
    const scrollOffset = e.nativeEvent.contentOffset.x;
    const activePage = Math.round(scrollOffset / this.props.swiperWidth);
    let stateParam: any = {
      currentPage: activePage,
    };
    stateParam.currentPage = this.fixFirstAndLastPos(activePage);
    this.setState(stateParam);
  };
  private getRemoveClippedSubviews(isRemoveClippedSubviews: boolean): any {
    if (PlatformUtils.isAndroid()) {
      return isRemoveClippedSubviews;
    }
    return false;
  };

  renderSwiperDot = (imgList: any, swiperItemWidth: number) => {
    return (
      <SwiperDots
        activeImgColorList={this.activeImgColorList}
        currentPage={this.state.currentPage}
        imgList={imgList}
        width={swiperItemWidth}
        isHarmonyStyle={true}
        activeDotColor={'red'}
        gestureEvent={this.gestureListener}
        defaultDotColor={CommonUtils.colorRgba('#000000', 0.1)}
      />
    );
  };

  clickToInfoPage = (orderCode: any) => {
    const url = `${env.wapDomain}bpreact/order/trace?orderCode=${orderCode}`;
    RouterUtils.gotoPage(url);
  };

  renderOneItem = (_styles, imgListViwApp) => {
    return (
      <View style={_styles.scheduleContent}>
        <View style={_styles.scheduleBody}>
          {imgListViwApp}
        </View>
      </View>
    );
  };

  renderScheduleList = (_styles, imgListViwApp, isRemoveClippedSubviews) => {
    const { latestOrderLogList, swiperWidth } = this.props;
    const onScroll = (e: any) => {
      this.gestureListener.triggerEvent('onMove', { value: e });
      this.onScroll(e);
    };
    return PlatformUtils.isWap(dsWindow.width) ? (
        <View style={_styles.scheduleContent}>
          <View style={_styles.scheduleSwiper}>
            <Swiper
              from={1}
              loop={true}
              timeout={7}
              auto={true}
              controlsProps={{
                prevPos: false,
                nextPos: false,
                dotsTouchable: true,
                dotProps: {
                  badgeStyle: _styles.dot,
                  containerStyle: _styles.dotBox,
                },
                dotActiveStyle: _styles.activeDot,
              }}
              imgListViwApp={imgListViwApp}
              springConfig={{ bounciness: 1 }}
            >
              {imgListViwApp}
            </Swiper>
          </View>
        </View>
      ) : (
        <View style={_styles.scheduleViewContent}>
          <View style={[{width: swiperWidth}, _styles.scheduleViewBody]}>
            <ScrollView
              key={latestOrderLogList?.length}
              ref={this.refScrollView}
              style={[{width: swiperWidth}, _styles.scheduleSwiperBody]}
              scrollEventThrottle={16}
              horizontal={true}
              contentOffset={{ x: swiperWidth, y: 0 }}
              showsHorizontalScrollIndicator={false}
              pagingEnabled={true}
              onScrollBeginDrag={this.scrollBeginDrag}
              onScrollEndDrag={this.scrollEndDrag}
              // 当一帧滚动结束
              onMomentumScrollEnd={this.onAnimatinonEnd}
              onScroll={onScroll}
              removeClippedSubviews={this.getRemoveClippedSubviews(isRemoveClippedSubviews)}
            >
              {imgListViwApp}
            </ScrollView>
            {this.renderSwiperDot(latestOrderLogList, swiperWidth)}
          </View>
        </View>
    );
  };

  render() {
    const _styles = WebScheduleStyle(DarkStore.theme);
    let insertNum = 0;
    const { latestOrderLogList, swiperWidth } = this.props
    if (latestOrderLogList.length <= 1) {
      this.imgListWap = latestOrderLogList;
    } else {
      // 为了模拟循环轮播的效果，在订单进度列表的第一个前加上最后一个订单，由于是pad规范要求，故在最后一个订单加上第一二个订单
      const latestIndex = 0 // 订单进度列表下标，此值用来取第一个数据，用来实现循环轮播
      const ary3 = [latestOrderLogList[latestIndex]];
      const ary1 = [latestOrderLogList[latestOrderLogList.length - 1]];
      this.imgListWap = ary1.concat(latestOrderLogList, ary3);
      insertNum = 1;
    }
    const imgListLen = this.imgListWap.length;
    let isRemoveClippedSubviews = true;
    const set = new Set();
    if (insertNum === 1) {
      set.add(1);
      set.add(imgListLen - 2);
    }
    isRemoveClippedSubviews = !set.has(this.state.currentPage);
    
    const imgListViwApp = this.imgListWap.map((val: any, index: number) => {
      const imgObj = {
        customImg: val.customImg,
        photoPath: val.photoPath,
        photoName: val.photoName,
      };
      const updateDate = val.updateDate ? TimeUtils.formatDate(new Date(val.updateDate.replace(/-/g, '/'))) : '';
      const imgUrl = handleImgUrl(imgObj);
      this.activeImgColorList[index] = DarkStore.theme.C17.color;
      return (
        <TouchableOpacity style={_styles.scheduleItem} activeOpacity={1} onPress={() => this.clickToInfoPage(val.orderCode)} {...this._gestureHandlers.panHandlers}>
          <View style={[{width: swiperWidth}, _styles.scheduleArea]}>
            <FastImageView
              imgUri={imgUrl}
              imgStyle={_styles.prdImg}
            />
            <View style={_styles.scheduleStatus}>
              <View style={_styles.scheduleDate}>
                <Text style={[PlatformUtils.isWap(dsWindow.width) ? _styles.displayStatusDescWap : _styles.displayStatusDesc]}>{val.displayStatusDesc}</Text>
                <Text style={_styles.updateDate}>{updateDate}</Text>
              </View>
              <View style={_styles.scheduleDesc}>
                <Text style={_styles.progressDesc} numberOfLines={fontStore.fontMutiple > FONT_MUTIPLE.FONT_LEVEL_ONE ? 2 : 1} ellipsizeMode={'tail'}>{val.progressDesc}</Text>
              </View>
            </View>
          </View>
        </TouchableOpacity>
      );
    });
    return imgListLen === 1 ? this.renderOneItem(_styles, imgListViwApp) : this.renderScheduleList(_styles, imgListViwApp, isRemoveClippedSubviews);
  }
}
export default OrderSchedule;
