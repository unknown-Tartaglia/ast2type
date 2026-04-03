/*
 * @Date: 2022-01-05 10:13:12
 * @Description: 个人中心APK页面引擎
 * @FilePath:
 */
import {
  CommonUtils,
  DataHandleUtils,
  DeviceUtils,
  PlatformUtils,
  RnBridge,
  screenSize as getScreenSize,
  TimeUtils,
  WithTheme,
  RecordUtils,
  EVENT_TYPE,
  EventTracking,
  HttpService,
  Service as env,
  ERROR_TYPE,
  MCP_PORTAL,
  MCP_LANG,
  MCP_COUNTRY,
  PAGE_TYPE,
  Http as http,
  appIdStore as AppidStore,
  LoginUtils,
  DynamicComponent,
  DarkStore,
  onLayout,
  layout,
  StorageUtil,
  APP_INFOS,
  groupTagsStore,
  Listener,
  LoginStore,
  configStore,
  AppStore,
  E2EIdStore,
  PAGE_TYPE_E2EID,
  FONT_MUTIPLE,
  ScreenUtils,
} from '@hw-vmall/vrn-basic-comp';
import {
  Toast,
  CommonErrorPage,
  pageHeaderStore,
  PlaceHolder,
  FixedButton,
  Product,
  LottieRefreshControl,
  jsonConvert,
  ScenePurchaseBottomNavLayout,
  LoginCompnent,
  NotifyCompnent,
} from '@hw-vmall/vrn-bussiness-comp';
import _ from 'lodash';
import { observer } from 'mobx-react';
import React from 'react';
import { Animated, DeviceEventEmitter, AppState, RefreshControl, View } from 'react-native';
import { GestureHandlerRootView } from 'react-native-gesture-handler';
import { DialogType } from '../../../../types/commonType';
import { MapComponents } from '../../../../common/maps/map-components';
import BirthdayGift from '../../component/birthdayGift';
import PersonalHead from '../../component/personal';
import PersonalTitle from '../../component/personal/personal-head';
import HomeStyle from './style';

const TAG: string = 'Personal';
const WAIT_TIME: number = 10 * 1000;
let iosBottomBarHeight: number = 0;
const CONSUME_YEAR_TYPE: string[] = ['1', '2']; // 1"：未成年账号 “2”表示儿童

const lottieViewHeight: number = 96;

// 获取iOS设备状态栏的高度
if (PlatformUtils.isIOS()) {
  DeviceUtils.getBottomBarHeight()
    .then((result: any) => {
      iosBottomBarHeight = result;
    })
    .catch((error: any) => {
      // do nothing
    });
}
// 添加防抖
let timeout: NodeJS.Timeout | null = null;
const debounce = (cb: () => any, wait = 500) => {
  if (timeout !== null) {
    clearTimeout(timeout);
  }
  timeout = setTimeout(() => {
    timeout = null;
    cb && cb();
  }, wait);
};
@observer
class Personal extends React.Component<any, any> {
  eventListener: any;
  appStateListener: any;
  eventListenerLogin: any;
  headStyle: any = {};
  groupStyleChanges: any = {};
  personalStyleChange: any = {};
  private scroller: any;
  strategyIdList = '';
  scrollViewStartOffsetY = 0;
  // 1-空页面 2-带子页签的空页面 3-分类页 4-个人中心 7-秒杀页
  pageType: number = 4;
  showBox: number = 1;
  configInfo: any;
  otherParams: any = {};
  refreshTimer: any;
  scrollViewKey: number = 1;
  refreshControl: LottieRefreshControl;
  upgradeGiftInterval: any = 0;
  lastGiftPopupTime: any = null;
  lastCalendarPopupTime: any = null;
  giftPoint: any = 0;

  /**
   *  enableAdvancedFeature为空（跟apk约定拿不到值返回-1）或者不等于0（enableAdvancedFeature=1代表同意）。enableAdvancedFeature=0，即用户不同意协议和隐私
   *  原通过与apk接口异步获取，有渲染问题，现改为使用bundle的props获取--apk传递本地缓存值(默认-1)
   */
  enableAdvancedFeature: number = Number(this.props.enableAdvancedFeature);
  calendarAuthLinstener: any = null;
  sonRef: any;
  animatedEvent: any;
  navOpacityAnimated: any;
  isPersonal: any = true;
  timer1: any;
  timer: any; // 适配IOS曝光
  strategyTimer: any;
  listerDialog: any; // 监听apk弹窗
  isLeave: boolean;
  pageCatCode: string = '';
  pageCatName: string = '';
  // 判断当前页面是否在可视窗口内
  isFocus: boolean = false;
  deviceRes: any;
  userId: string;
  dialogEventLisenter: any = null;
  isGroupFlag: boolean = false;
  isDisplayScenePurchaseNavBottom: boolean = false; // 是否展示场景购的底部导航
  scenePurchaseNavBottomData: any = {}; // 场景购底部导航的数据
  pageListener: Listener = new Listener('Personal');
  hmiSpanIdFirstScreen: string; // firstScreen begin埋点返回的数据，里面有spanId
  hmiSpanIdFinalScreen: string; // finalScreen begin埋点返回的数据，里面有spanId
  getRecommendFlagTimer: any;
  isCaculated: boolean = false;
  consumeYear: string = '1';
  remainDays: number = 30;
  recyclerListOneByTwo: boolean = true; // 商品卡1*2样式是否使用recyclerList加载
  eventOffsetY: any;
  constructor(props: any) {
    super(props);
    this.state = {
      scrollY: new Animated.Value(0),
      pageId: this.props.pageId,
      reportPageId: this.props.mineData?.pageInfos?.length
        ? this.props.mineData?.pageInfos[0]?.pageId
        : this.props.pageId,
      cmsData: { pageInfos: [] },
      // loading标记
      loading: true,
      // 防止连续下拉
      isRefreshing: false,
      // error标记
      error: false,
      configInfo: '',
      cartNum: this.props.firstCart || 0, // 购物车数量
      messageNum: this.props.firstMessage || 0, // 消息中心数量
      titleOpacity: new Animated.Value(0),
      errorType: ERROR_TYPE.OTHER_ERROR,
      isJsLogin: this.props.isLogin,
      avaImg: this.props.avaImg || '',
      userName: this.props.userName || '',
      userLevel: this.props.userLevel || 0,
      userAccount: this.props.userAccount,
      templateContent: '',
      dialogType: '',
      productTitleAndMore: null,
      isVpro: this.props.isVpro === true || this.props.isVpro === 'true' ? '1' : '0', // 返回值为字符串类型时，ios生效，否则是apk生效
      isShowMember: false,
      getVproLogoFinish: false, // 付费会员logo是否请求完成
      withNoLoginUser: 0,
      tid: '',
      recommendFlag: false,
      isShow: true,
      isShowNotifyDialog: false,
      sysNoticeShow: 0,
      sysNoticeBtnTxt: '',
      sysNoticeTxt: '',
      system: '',
      logistics: '',
      service: '',
      activity: '',
      shortMessage: '',
    };
    this.rnBundleLoadEnd();
    this.getSwitchConfig();
    this.lastGiftPopupTime = this.props.lastPopupTime || null; // null防止lastPopupTime是undefined，代码中使用时判断出错
    this.lastCalendarPopupTime = this.props.lastCalendarPopupTime || null; // null防止lastCalendarPopupTime是undefined
    this.otherParams.isLogin = props.isLogin;
    this.otherParams.uniqueId = props.uniqueId;
    this.otherParams.pageListener = this.pageListener;
    this.otherParams.oaid = this.props.oaid || '';
    if (this.props.abTest) {
      let ab: any = JSON.parse(this.props.abTest);

      if (ab instanceof Array) {
        this.setAbData(ab);
      }
    }
    this._onRefresh = this._onRefresh.bind(this);
    RecordUtils.info(
      TAG,
      `constructor
       enableAdvancedFeature=${this.props.enableAdvancedFeature}
       typeof=${typeof this.props.enableAdvancedFeature}`,
    );
    this.getDeviceTid();
  }

  getSwitchConfig() {
    const couponConfig: boolean | undefined = configStore.couponUseConfig;
    if (couponConfig === undefined) {
      CommonUtils.getConfigByKey('is_open_rn_coupon_use', true).then((res) => {
        if (typeof res === 'boolean') {
          configStore.setCouponUseEnable(res);
        }
      });
    }
  }

  rnBundleLoadEnd = async () => {
    if (PlatformUtils.isAndroid()) {
      const { e2eId, parentSpanId, mineData } = this.props;
      DeviceUtils.hmiLog({
        e2eId,
        parentSpanId,
        stage: 'end',
        name: 'rnBundleLoad',
      });
      if (!mineData?.pageInfos) {
        this.hmiSpanIdFirstScreen = await DeviceUtils.hmiLog({
          e2eId,
          parentSpanId,
          stage: 'begin',
          name: 'firstScreen',
        });
      }
    }
  };

  componentDidUpdate(prevProps: any) {
    if (this.props.isLogin !== prevProps.isLogin) {
      this.setState({ isJsLogin: this.props.isLogin }, () => {
        if (this.props.isLogin) {
          this.updateSonRef();
          this._queryUserInfo();
          this.getSysConfig();
        }
      });
    }
  }

  // 处理apk弹窗策略信息
  handleStrategy() {
    // showBox不存在或为空时，需要走拉弹窗流程
    const showBox = this.showBox === 0 ? 0 : this.showBox || 1;
    // 判断特性开关是否开启
    if ((PlatformUtils.isAndroid() || PlatformUtils.isHarmony()) && showBox === 1) {
      RnBridge.invokeVmallNative('common', 'setCurrentPrdId', {
        pageId: this.state.pageId,
        from: 'personalpage',
      });
      this.listerDialog = this.handleListerDialog();
    }
  }

  private handleListerDialog(): any {
    return DeviceEventEmitter.addListener('NativeCallAction', (event: any) => {
      const popStrategies = event?.param?.popStrategies && JSON.parse(event.param.popStrategies);
      const activityCode = popStrategies?.activityCode;
      const strategyContent = popStrategies?.strategyContent;
      const strategies = strategyContent?.strategies;
      if (event?.action === 'popStrategies' && activityCode && !strategyContent) {
        this.popStrategyDialog(activityCode);
      }
      this.handlePopStrategies(event, activityCode, strategyContent, strategies);
    });
  }

  private handlePopStrategies(event: any, activityCode: any, strategyContent: any, strategies: any) {
    if (event?.action === 'popStrategies' && activityCode && strategyContent && strategies?.length) {
      const timeSeconds = strategies[0].timeSeconds;
      this.strategyTimer = setTimeout(() => {
        this.popStrategyDialog(activityCode);
      }, timeSeconds * 1000);
    }
  }

  // 调用apk弹窗接口弹窗
  popStrategyDialog(activityCode: string) {
    RnBridge.invokeVmallNative('common', 'popStrategyDialog', {
      popParams: {
        activityCode,
        pageId: this.state.pageId,
        from: 'personalpage',
      },
    });
  }

  handleAppStateChange = (appState: any) => {
    // active：前台运行中 background：后台运行中 inactive：运行的过渡状态
    if (appState === 'active') {
      this.getNotifyInfo();
    }
  };

  async componentDidMount() {
    DeviceUtils.setBarStyle('dark-content');
    this.closeLoading();
    this.getVproLogo();
    this.getAppLoginAndGroupInfo();
    let { mineData, isLogin, avaImg, userName, pageId, userAccount } = this.props;
    this.handlePreLoadData();
    this.eventTracingReportByLoad(); // 首次进入需要上报
    this.handlePageInfo();
    await this.getLoginData(isLogin, avaImg, userName, userAccount);
    this._isLogin();
    // 清明节模式
    this.handleQmMode();
    TimeUtils.updateSystemTime();
    if (PlatformUtils.isApp()) {
      RnBridge.invokeVmallNative('common', 'getCartAndMessageNmb', {}).then((result: any) => {
        const messageNum = result.firstMessage && JSON.parse(result.firstMessage);
        this.setState({
          messageNum: messageNum ? messageNum : 0,
        });
      });
      this.appStateListener = PlatformUtils.isIOS() && AppState.addEventListener('change', this.handleAppStateChange);
      this.eventListener = DeviceEventEmitter.addListener('NativeCallAction', (event) => {
        this.handleCarNum(event);
        this.handleMessageNum(event);
        // 监听消息浮层状态
        this.handleNotifiactionStatus(event);
        // 埋点上报
        this.handleReport(mineData, pageId, event);
        // 网络刷新
        this.personNetworkRefresh(event, isLogin, avaImg, userName, userAccount);
        // 个人中心离开
        this.personPageLeave(event);
      });
    }
    // 个人中心顶部状态栏设置
    this.setStatusBarStyle();
    this.dialogEventLisenter = DeviceEventEmitter.addListener('getBenefitSucc', () => {
      this.sonRef?.getAssterInfo();
    });
    this.getNotifyInfo();
  }

  private handleMessageNum(event: any) {
    if (event?.service === 'message' && event?.action === 'messageNum') {
      if (event?.param?.num) {
        this.setState({
          messageNum: event?.param?.num || 0,
        });
      }
    }
  }

  private handleCarNum(event: any) {
    if (event?.service === 'car' && event?.action === 'carNum') {
      if (event?.param?.num) {
        this.setState({
          cartNum: event?.param?.num || 0,
        });
      }
    }
  }

  private handlePreLoadData() {
    // 预加载数据
    if (this.props.mineData?.pageInfos) {
      RecordUtils.info(TAG, 'componentDidMount 预加载');
      this.handleData(this.props.mineData);
    }
  }

  private getAppLoginAndGroupInfo() {
    LoginUtils.getAppLoginAndGroupInfo().then((result: any) => {
      if (result) {
        groupTagsStore.setgroupTags(JSON.parse(JSON.stringify(result)));
      }
    });
  }

  private handleQmMode() {
    if (DarkStore.QMbool) {
      DeviceUtils.setTombStyle()
        .then(() => {})
        .catch();
    }
  }

  private async getLoginData(isLogin: any, avaImg: any, userName: any, userAccount: any) {
    if (isLogin) {
      this.getRecommendFlag(isLogin);
      await DeviceUtils.getDeviceInfo(APP_INFOS.DEVICE_INFO)
        .then((res) => {
          this.userId = res?.uid;
        })
        .finally(() => {});
      this._queryUserInfo(avaImg, userName, userAccount);
      this.getSysConfig();
    }
  }

  private handlePageInfo() {
    // 如果不存在则去调接口
    if (!this.props.mineData?.pageInfos) {
      this._getPageInfo();
    } else {
      this.handleStrategy();
    }
  }

  private handleReport(mineData: any, pageId: any, event: any) {
    let reportPageId = mineData?.pageInfos?.length ? mineData?.pageInfos[0]?.pageId : pageId;
    if (Number(event?.param?.currentIndex) === 4 && event.param.isCurrentIndex) {
      this.isLeave = true;
      // 页面将事件传递给监听这个事件的子组件
      RecordUtils.info(TAG, 'isPageShow personal come in');
      this.pageListener.triggerEvent('pageShow', { isPageShow: true });
      this.getNotifyInfo();
      debounce(() => {
        this.reportLoadPersonPage(reportPageId);
      }, 1000);
    } else if (
      Number(event?.param?.currentIndex) === 4 &&
      (event.param.isCurrentIndex === false || event.param.isCurrentIndex === 'false') &&
      this.isLeave
    ) {
      // 页面将事件传递给监听这个事件的子组件
      this.pageListener.triggerEvent('pageShow', { isPageShow: false });
      RecordUtils.info(TAG, 'isPageShow personal come out');
      this.isLeave = false;
      this.reportLeavePersonPage(reportPageId);
    }
  }

  private reportLeavePersonPage(reportPageId: any) {
    EventTracking.eventTracingReport({
      actionCode: '110000011',
      actionName: '离开个人中心页面上报',
      eventType: EVENT_TYPE.EVENT_TYPE_LEAVE,
      pageId: String(reportPageId),
      content: {},
      pageCatCode: this.pageCatCode,
      pageCatName: this.pageCatName,
      resSiteCode: '',
      resSiteName: '',
    });
  }

  private reportLoadPersonPage(reportPageId: any) {
    EventTracking.eventTracingReport({
      actionCode: '110000000',
      actionName: '加载个人中心组件化页面',
      eventType: EVENT_TYPE.EVENT_TYPE_LOADING_PAGE,
      pageId: String(reportPageId),
      content: {
        load: '1',
      },
      pageCatCode: this.pageCatCode,
      pageCatName: this.pageCatName,
      resSiteCode: '',
      resSiteName: '',
    });
  }

  private personNetworkRefresh(event: any, isLogin: any, avaImg: any, userName: any, userAccount: any) {
    if (event?.service === 'netWork' && event?.action === 'refresh') {
      if (this.state.error) {
        if (isLogin) {
          this._queryUserInfo(avaImg, userName, userAccount);
        } else {
          RnBridge.invokeVmallNative('common', 'invokingAutoLogin', {});
        }
        this.handleAbInfo(event);
        this.errorRefresh();
      }
    }
  }

  private handleAbInfo(event: any) {
    if (event?.param?.abInfo !== null) {
      const abInfo = CommonUtils.jsonParse(event.param.abInfo);
      const tabInfosList = abInfo.tabInfos || [];
      for (let index = 0; index < tabInfosList.length; index++) {
        if (tabInfosList[index].tabType === 'personal_center') {
          this.setState(
            {
              pageId: tabInfosList[index].relatedPage,
              pageAlias: '',
            },
            () => this.errorRefresh(),
          );
        }
      }

      if (abInfo.strategyInfoList instanceof Array) {
        this.setAbData(abInfo.strategyInfoList);
      }
      this.enableAdvancedFeature = 1;
    }
  }

  private personPageLeave(event: any) {
    if (
      event?.service === 'page' &&
      event?.action === 'pageLeave' &&
      this.props.uniqueId === event?.param?.uniqueId &&
      (PlatformUtils.isAndroid() || PlatformUtils.isHarmony())
    ) {
      if (event.param.isLeave) {
        this.getNotifyInfo();
        // apk 原生端原本在底部Tab切换到个人中心时设置了对应的状态栏颜色，故RN在维护个人中心状态栏时做对应处理
        if (PlatformUtils.isAndroid()) {
          this.setStatusBarStyle();
        }
        this.handleStrategy();
        CommonUtils.storeE2eId(PAGE_TYPE_E2EID.personal, false, E2EIdStore.residentPageE2EId[PAGE_TYPE_E2EID.personal]);
      } else {
        CommonUtils.storeE2eId(PAGE_TYPE_E2EID.personal, false);
        this.strategyTimer && clearTimeout(this.strategyTimer);
        this.listerDialog && this.listerDialog.remove();
      }
    }
  }

  // 消息浮层打开状态下，监听状态
  private handleNotifiactionStatus(event: any) {
    if (event?.service === 'notification' && event.action === 'notificationStatus') {
      if (PlatformUtils.isHarmony()) {
        this.getNotifyInfo();
        return;
      }
      if (this.state.isShow) {
        this.setState({
          isShow: false,
        });
      }
    }
  }

  /**
   * 修改背景：个人中心头部背景切换成白色背景，原本apk侧在tab切换默认设置的白色与当前背景颜色反差不明显
   * 普通账号：白色头部背景，状态栏黑色；
   * V+账号：黑色头部背景，状态栏白色；
   */
  setStatusBarStyle = () => {
    const vproList =
      this.state?.cmsData?.pageInfos?.length && JSON.parse(JSON.stringify(this.state.cmsData.pageInfos[0])).cards[0];
    const disPlayApk = vproList.configInfo && JSON.parse(vproList.configInfo)?.display;
    const isMember = this.getIsMember(disPlayApk);
    if (isMember) {
      DeviceUtils.setBarStyle('light-content');
    } else {
      DeviceUtils.setBarStyle('dark-content');
    }
  };

  UNSAFE_componentWillMount() {
    this.animatedEvent = Animated.event([
      {
        nativeEvent: {
          contentOffset: { y: this.state.scrollY }, // 将y值保存到state中背景色偏移距离的值上
        },
      },
    ]);
    const navOpacityOffset = this.state.scrollY;
  }

  componentWillUnmount() {
    this.eventListener && this.eventListener.remove();
    this.timer1 && clearTimeout(this.timer1);
    this.eventListenerLogin && this.eventListenerLogin.remove();
    this.appStateListener && this.appStateListener.remove();
    this.calendarAuthLinstener?.remove();
    this.state.scrollY && this.state.scrollY.removeAllListeners();
    if (PlatformUtils.isIOS()) {
      this.refreshTimer && clearTimeout(this.refreshTimer);
    }
    this.timer && clearTimeout(this.timer);
    if (PlatformUtils.isAndroid() || PlatformUtils.isHarmony()) {
      this.strategyTimer && clearTimeout(this.strategyTimer);
      this.listerDialog && this.listerDialog.remove();
    }
    this.dialogEventLisenter?.remove();
    this.getRecommendFlagTimer && clearTimeout(this.getRecommendFlagTimer);
  }

  // 获取个性化推荐开关
  getRecommendFlag = (isLogin: boolean) => {
    if (isLogin) {
      CommonUtils.getRecommendConfigRes().then((res) => {
        this.setRecommendFlag(res);
      });
    } else {
      this.setRecommendFlag(false);
    }
  };

  setRecommendFlag = (recommendFlag) => {
    if (this.state.recommendFlag !== recommendFlag) {
      this.setState({
        recommendFlag,
      });
    }
  };

  // 页面载入的埋点
  eventTracingReportByLoad = (isRefresh?: boolean) => {
    this.isLeave = true;
    EventTracking.eventTracingReport({
      actionCode: '110000000',
      actionName: '加载个人中心组件化页面',
      eventType: EVENT_TYPE.EVENT_TYPE_LOADING_PAGE,
      pageId: this.state.reportPageId?.toString(),
      content: {
        load: isRefresh ? '2' : '1',
      },
      pageCatCode: this.pageCatCode,
      pageCatName: this.pageCatName,
      resSiteCode: '',
      resSiteName: '',
    });
  };

  /**
   * 获取tid
   */
  getDeviceTid = () => {
    DeviceUtils.getDeviceInfo(APP_INFOS.DEVICE_INFO).then((res) => {
      this.setState({
        tid: res?.tid,
      });
    });
  };

  // 回到顶部
  onBackTop = () => {
    if (PlatformUtils.isIOS()) {
      setTimeout(() => {
        this.scroller && this.scroller.scrollToTop && this.scroller.scrollToTop(true);
        this.scroller && this.scroller.scrollTo && this.scroller.scrollTo({ y: 0, animated: true });
      }, 0);
    } else {
      this.scroller && this.scroller.scrollToTop && this.scroller.scrollToTop(true);
      this.scroller && this.scroller.scrollTo && this.scroller.scrollTo({ y: 0, animated: true });
    }
  };
  // 下拉刷新
  _onRefresh() {
    let { avaImg, userName, userAccount } = this.state;
    if (PlatformUtils.isIOS()) {
      LoginUtils.getLoginStatus().then((result: any) => {
        this.setState({
          isJsLogin: result,
        });
        if (result) {
          this.updateSonRef();
          // ios初始从hms获取昵称，下拉刷新从eop取昵称做了超长处理和hms返回值不一致,ios下拉刷新暂不更新用户名和昵称
          this._queryUserInfo(avaImg, userName, userAccount);
        }
      });
    }
    if (!PlatformUtils.isIOS() && this.state.isJsLogin) {
      this.updateSonRef();
      this._queryUserInfo();
    }
    this.getRecommendFlag(this.state.isJsLogin);
    // 执行子组件方法
    if (this.state.isRefreshing) {
      return Promise.resolve();
    }
    if (PlatformUtils.isIOS()) {
      this.setState({
        isRefreshing: true,
      });
      DeviceEventEmitter.emit('onRefresh', PAGE_TYPE.personal); // IOS通过触发下拉刷新事件规避部分组件需要卸载更新数据源
      this.refreshTimer && clearTimeout(this.refreshTimer);
      this.refreshTimer = setTimeout(() => {
        this.setState({ isRefreshing: false });
      }, 1000);
    } else {
      this.scrollViewKey = this.scrollViewKey + 1;
    }
    DeviceEventEmitter.emit('homeRefresh', PAGE_TYPE.personal); // 针对瀑布流，下拉刷新时，把猜你喜欢重置
    // 更新数据
    TimeUtils.updateSystemTime();
    // 直接调用接口
    this._getAndroidPageInfo(true);
    this.getNotifyInfo();
  }
  // 调用子组件方法
  refSon = (ref) => {
    this.sonRef = ref;
  };
  updateSonRef = () => {
    if (this.sonRef) {
      this.sonRef.getAssterInfo();
      this.sonRef.getAssterInfoOrder();
      this.sonRef.getScheduleInfoOrder();
    }
  };
  setAbData(list: Array<any>) {
    let abArr = list?.map((el) => {
      return el.strategyId || '';
    });
    this.strategyIdList = JSON.stringify(abArr);
  }
  isAndroid = () => {
    return PlatformUtils.isAndroid();
  };
  _queryUserInfo = (avgImg?: any, userName?: any, userAccount?: any) => {
    HttpService.getUserInfo(MCP_PORTAL.APP, MCP_LANG.CN, MCP_COUNTRY.CN, false)
      .then((user: any) => {
        const uid = user?.userInfo?.uid;
        const consumeYear = user?.userInfo?.consumeYear;
        AppStore.setUserInfo(user?.userInfo);
        if (uid && !this.userId) {
          this.userId = uid;
        }
        if (consumeYear) {
          this.consumeYear = consumeYear;
        }
        this.getNotifyInfo();
        if (CommonUtils.isEmpty(user?.userInfo)) {
          return;
        }
        this.handleUserInfo(user, avgImg, userName, userAccount);
        const isVipJudge = user?.userInfo?.isVpro;
        if (this.state.isVpro === isVipJudge || !isVipJudge) {
          return false;
        } else {
          this.setState(
            {
              isVpro: isVipJudge,
            },
            () => {
              this.setStatusBarStyle();
            },
          );
        }
      })
      .catch(() => {
        this.otherParams.userInfo = null;
        RecordUtils.error(TAG, 'getUserInfo fail');
      });
  };

  /**
   *
   * @param id 接收APK 传递参数
   * @returns 预加载处理
   */
  handleData = (data?: any) => {
    DataHandleUtils.initCardsList(data, 'app');
    DataHandleUtils.oneTimeCallPageDataSource(data?.pageInfos);
    if (data?.pageInfos?.length) {
      const { pageCatCode, pageCatName, pageType, groupStyleChanges, styleChange, headerStyle, pageParam } =
        data?.pageInfos[0] || {};
      this.pageCatCode = pageCatCode;
      this.pageCatName = pageCatName;
      this.groupStyleChanges = groupStyleChanges ? JSON.parse(groupStyleChanges) : '';
      this.personalStyleChange = styleChange ? JSON.parse(styleChange) : {};
      this.headStyle = headerStyle ? JSON.parse(headerStyle) : {};
      this.pageType = pageType;
      this.otherParams.hasTitle = !!this.headStyle?.headStyle;
      const param = pageParam && JSON.parse(pageParam);
      this.showBox = param?.showBox;
      const { sysNoticeShow, sysNoticeBtnTxt, sysNoticeTxt } = this.headStyle;
      this.setState({
        sysNoticeBtnTxt,
        sysNoticeTxt,
        sysNoticeShow,
        cmsData: data,
        configInfo: JSON.stringify(this.headStyle?.attribute),
        withNoLoginUser: param?.withNoLoginUser,
      });
    }
    const channel = data?.pageInfos?.length && data.pageInfos[0].channel;
    AppidStore.getAppId(channel);
  };

  /**
   * 获取Android pageID和AB策略
   * @private
   */
  _getAndroidPageInfo = (isRefresh?: boolean) => {
    if (!this.state.pageId && this.enableAdvancedFeature !== 0) {
      return PlatformUtils.isHarmony() ? Promise.reject(new Error('Network Error')) : Promise.reject();
    }
    let pageId = this.state.pageId;
    let pageAlias = '';
    if (this.enableAdvancedFeature === 0) {
      pageId = '';
      pageAlias = 'rnBasicPersonalPage';
    }
    RecordUtils.info(TAG, 'pageId=' + pageId + '---this.props.pageId=' + this.props.pageId);
    let getPageInfoPromise = new Promise((resolve) =>
      resolve(HttpService.getPageInfoListAsyncForApk(pageId, this.strategyIdList, '3', pageAlias)),
    );

    let fasterPromise = CommonUtils.racePromise(getPageInfoPromise, WAIT_TIME);
    return fasterPromise
      .then((data: any) => {
        if (data?.message?.includes('Network Error')) {
          RecordUtils.error(TAG, 'overtime1 pageId:' + pageId);
        }
        data = DataHandleUtils.initCardsList(data, 'app');
        this.handleData(data);
        this.updateReportPageId(data, isRefresh);
        return Promise.resolve();
      })
      .catch((e) => {
        this.getAndroidPageInfoCatch(isRefresh, e);
      })
      .finally(() => {
        !isRefresh && this.handleStrategy();
      });
  };

  private updateReportPageId(data: any, isRefresh: boolean) {
    this.setState(
      {
        reportPageId: data?.pageInfos?.length && data.pageInfos[0]?.pageId,
      },
      () => {
        this.eventTracingReportByLoad(isRefresh);
      },
    );
  }

  private getAndroidPageInfoCatch(isRefresh: boolean, e: any) {
    if (!isRefresh && e?.message?.includes('Network Error')) {
      RecordUtils.error(TAG, '_getAndroidPageInfo ERROR_TYPE.NETWORK_ERROR');
      this.setState({
        errorType: ERROR_TYPE.NETWORK_ERROR,
        error: true,
      });
    } else {
      RecordUtils.error(TAG, '_getAndroidPageInfo fail ' + e?.stack);
      this.reportHmiException(e?.message);
    }
  }

  private handleUserInfo(user: any, avgImg: any, userName: any, userAccount: any) {
    this.otherParams.userInfo = user?.userInfo;
    if (user?.userInfo?.groupId) {
      StorageUtil.setSpValueAll('isGroupUser', 'true', 'String');
      StorageUtil.setSpValueAll('groupflag', 'true', 'String');
      StorageUtil.setSpValueAll('user_group_id', user?.userInfo?.groupId?.toString(), 'String');
      StorageUtil.setSpValueAll('user_group_name', user?.userInfo?.groupName?.toString(), 'String');
      this.isGroupFlag = true;
    } else {
      StorageUtil.setSpValueAll('isGroupUser', 'false', 'String');
      StorageUtil.setSpValueAll('groupflag', '', 'String');
      if (PlatformUtils.isAndroid() || PlatformUtils.isHarmony()) {
        StorageUtil.setSpValueAll('user_group_id', '', 'String');
      }
      this.isGroupFlag = false;
    }
    this.updateUserInfo(user, avgImg, userName, userAccount);
  }

  private updateUserInfo(user: any, avgImg: any, userName: any, userAccount: any) {
    if (this.isRefresh(user)) {
      this.setState({
        userLevel: user?.userInfo?.custGrad,
        avaImg: avgImg ?? user?.userInfo?.custHeaderImg,
        userName: userName ?? user?.userInfo?.nickName,
        userAccount: userAccount ?? user?.userInfo?.userAccount,
      });
    }
  }

  private isRefresh(user: any) {
    return (
      this.state.avaImg !== user?.userInfo?.custHeaderImg ||
      this.state.userName !== user?.userInfo?.nickName ||
      this.state.userLevel !== user?.userInfo?.custGrad ||
      this.state.userAccount !== user?.userInfo?.userAccount
    );
  }

  reportHmiException(error: any) {
    if (!CommonUtils.isEmpty(error)) {
      DeviceUtils.hmiLogForEventSpan({
        eventType: 'page_error_load_data_fail',
        extraInfo: {
          error: error,
          info: JSON.stringify('个人中心加载异常，数据加载失败, 页面id: ' + this.state.pageId),
        },
      });
    }
  }

  reportHmiEnd() {
    if (PlatformUtils.isAndroid()) {
      const { e2eId, parentSpanId, mineData } = this.props;
      const data = this.state.cmsData;
      const pageName = data?.pageInfos?.length && data.pageInfos[0]?.pageName;
      if (!mineData?.pageInfos) {
        DeviceUtils.hmiLog({
          e2eId,
          parentSpanId,
          stage: 'end',
          name: 'finalScreen',
          spanId: this.hmiSpanIdFinalScreen,
        });
      }
      DeviceUtils.hmiLog({
        e2eId,
        parentSpanId,
        stage: 'end',
        name: 'entry',
        reportNow: 'true',
        spanId: parentSpanId,
        content: {
          category: 'RN我的页',
          instanceId: this.state.pageId,
          instanceName: pageName,
        },
      });
    }
  }

  // eslint-disable-next-line @typescript-eslint/no-unused-vars
  _getPageInfo(data?: boolean) {
    return this._getAndroidPageInfo()
      .catch((e) => {
        // 网络错误
        if (e?.message?.includes('Network Error')) {
          RecordUtils.error(TAG, '_getPageInfo ERROR_TYPE.NETWORK_ERROR');
          this.setState({
            errorType: ERROR_TYPE.NETWORK_ERROR,
          });
        } else {
          RecordUtils.error(TAG, '_getPageInfo ERROR_TYPE.OTHER_ERROR ' + e?.stack);
          // 其他错误
          this.setState({
            errorType: ERROR_TYPE.OTHER_ERROR,
          });
          this.reportHmiException(e?.message);
        }
        // 流程出错
        this.isPersonal = false;
        this.setState({
          error: true,
          // isPersonal: false
        });
      })
      .finally(async () => {
        if (PlatformUtils.isAndroid()) {
          const { parentSpanId, e2eId } = this.props;
          DeviceUtils.hmiLog({
            e2eId,
            parentSpanId,
            stage: 'end',
            name: 'firstScreen',
            spanId: this.hmiSpanIdFirstScreen,
          });
          this.hmiSpanIdFinalScreen = await DeviceUtils.hmiLog({
            e2eId,
            parentSpanId,
            stage: 'begin',
            name: 'finalScreen',
          });
        }
        // 结束loading状态
        this.setState({
          loading: false,
          isRefreshing: false,
        });
        return Promise.resolve();
      });
  }

  closeLoading() {
    RnBridge.invokeVmallNative('page', 'loaded', {});
  }

  _onMomentumScrollEnd = (e: any) => {
    if (PlatformUtils.isHarmony()) {
      return;
    }
    // 监听页面滚动事件
    DeviceEventEmitter.emit('onScrollEvent', e, 'personal');
  };

  _onScrollBeginDrag = (e: any) => {
    // 监听页面滚动开始事件
    DeviceEventEmitter.emit('onScrollBeginDragEvent', e, PAGE_TYPE.personal);
    this.scrollViewStartOffsetY = e.nativeEvent.contentOffset.y;
  };

  _onScrollEndDrag = (e: any) => {
    // 处理ScrollView/RecyclerWaterfallList滑到最顶或最底部后再次滑动，单框架RN不回调_onMomentumScrollEnd导致浮标隐藏后不会再次显示问题
    if (PlatformUtils.isHarmony()) {
      this.timer && clearTimeout(this.timer);
      this.timer = setTimeout(() => {
        const event = {
          nativeEvent: {
            contentOffset: { x: 0, y: this.eventOffsetY },
          },
        };
        DeviceEventEmitter.emit('onScrollEvent', event, PAGE_TYPE.personal);
      }, 1000);
    }
  };

  _onLayout = (e: any) => {
    onLayout(e);
    layout(e, PAGE_TYPE.personal);
  };

  dialogTimer: any = null;
  flag: any = true; // 走个人中心的逻辑
  // 获取升级礼包、生日礼包领取弹窗间隔时间配置、生日礼包日历间隔时间配置
  getSysConfig = async () => {
    const { enableAdvancedFeature } = this.props;
    // 简易版个人中心不用弹升级礼包领取提醒、生日礼包领取提醒和下月生日礼包日历提醒
    if (enableAdvancedFeature === 0 || enableAdvancedFeature === '0') {
      return null;
    }
    await this.getGiftConfig();
    if (this.lastGiftPopupTime == null || new Date().getTime() - this.lastGiftPopupTime > this.upgradeGiftInterval) {
      this.getUpgradePrivileges();
    }
    // }, 100)
  };

  // 获取升级礼包、生日礼包领取弹窗间隔时间配置
  getGiftConfig = () => {
    return new Promise((resolve) => {
      HttpService.querySystemConfig(`['GIFT_NOTICE_POPUP_INTERVAL', 'GIFT_CALENDAR_POPUP_INTERVAL']`).then((res) => {
        if (res.systemConfigInfos) {
          this.upgradeGiftInterval =
            res.systemConfigInfos.GIFT_NOTICE_POPUP_INTERVAL?.systemConfigValue * 24 * 3600 * 1000 || 0;
          resolve({});
        }
      });
    });
  };

  // 升级礼包的弹出逻辑
  handleUpgradeData(upgradeRights) {
    let rights = JSON.parse(JSON.stringify(upgradeRights));
    // 按level从小到大排序
    function compare(pro) {
      return function (a, b) {
        const val1 = a[pro];
        const val2 = b[pro];
        return val2 - val1;
      };
    }
    rights = rights.sort(compare('level'));
    // 找到符合条件的就停止循环，否则继续查询
    let sum = 0;
    for (let i = 0; i < rights.length; i++) {
      const right = rights[i];
      if (Number(right?.validate) === 1 && Number(right?.received) === 0) {
        sum++;
        this.giftPoint = right?.giftPoint || 0;
        this.getBirthTemplate(DialogType.POP_UP_UPGRADE_MODAL);
        this.setLastBirthPopupTime(new Date().getTime());
        break;
      }
    }
    if (sum === 0) {
      this.getBirthdayPrivileges();
    }
  }

  // 获取升级礼包权益
  getUpgradePrivileges = () => {
    const url = `${
      env.openApiDomain
    }mcp/user/upgradeGift?portal=${CommonUtils.getPortal()}&country=CN&lang=zh_CN&version=1`;
    http.get(url).then((res) => {
      if (String(res.code) === '50020') {
        // 被风控 用户无感知 流程结束
      } else if (String(res.code) !== '0') {
        // 接口异常 用户无感知 流程继续
        this.getBirthdayPrivileges();
      } else {
        if (res.count > 0) {
          this.handleUpgradeData(res?.lstgiftRights);
        } else {
          this.getBirthdayPrivileges();
        }
      }
    });
  };

  // 获取生日礼包权益
  getBirthdayPrivileges = () => {
    const url = `${
      env.openApiDomain
    }mcp/user/birthdayPrivileges?portal=${CommonUtils.getPortal()}&country=CN&lang=zh_CN&version=1`;
    http.get(url).then(async (res) => {
      if (String(res.code) === '50020') {
        // 被风控 用户无感知 流程结束
      } else if (res.success) {
        const currentMonthRemind = res?.currentMonthRemind;
        this.giftPoint = res?.giftPoint;
        if (currentMonthRemind) {
          this.setState({
            dialogType: DialogType.POP_UP_BIRTHDAY_MODAL,
          })
          this.setLastBirthPopupTime(new Date().getTime());
        }
      }
    });
  };

  // 计算时间
  caculteDate = () => {
    const time = new Date();
    let year = time.getFullYear();
    let month = time.getMonth();
    if (month === 11) {
      year += 1;
      month = 0;
    } else {
      month += 1;
    }
    const startTime = new Date(year, month, 1, 10);
    const endTime = new Date(year, month, 1, 24);
    return { begin: startTime.getTime(), end: endTime.getTime() };
  };

  // 设置或创建上次升级生日弹窗时间
  setLastBirthPopupTime = (time) => {
    StorageUtil.setSpValueAll('last_popup_time', time.toString(), 'String');
  };

  birthTemplate: any = null;
  // 获取模板
  getBirthTemplate = (type) => {
    clearTimeout(this.birthTemplate);
    this.birthTemplate = setTimeout(() => {
      if (!this.isPersonal) {
        return;
      }
      const portal = CommonUtils.getPortal();
      const url = `${env.openApiDomain}mcp/queryTemplate?portal=${portal}&country=CN&lang=zh_CN&version=1&placeholder=['${type}']`;
      http.get(url, {}).then((res) => {
        this.setState({
          dialogType: type,
          templateContent: res?.templateMapping && res?.templateMapping[type].content,
        });
      });
    }, 300);
  };
  // 付费会员logo
  getVproLogo = () => {
    const holderParams = 'vmall_vpro_logo';
    HttpService.getTemplate(holderParams)
      .then((res) => {
        if (res?.success) {
          const tmpMap: any = res.templateMapping;
          const tagHolder = tmpMap?.vmall_vpro_logo?.content?.replace(/<.*?>/gi, '');
          this.otherParams.vproLogoTagHolder = tagHolder;
        }
      })
      .finally(() => {
        this.setState({
          getVproLogoFinish: true,
        });
      });
  };

  // 关闭弹窗，修改dialogType
  changeDialog = () => {
    this.setState({
      dialogType: '',
      templateContent: '',
    });
  };
  render() {
    return (
      <WithTheme themeStyles={HomeStyle}>
        {(styles, theme) => {
          const placeholderContent =
            !this.state.isRefreshing && this.state.loading ? (
              <PlaceHolder Fade={true} />
            ) : (
              ((this.state.pageId || this.enableAdvancedFeature === 0) &&
                this.state.cmsData &&
                this.state.cmsData.pageInfos?.length &&
                !this.state.error &&
                this.renderPage(styles, theme)) || (
                <CommonErrorPage
                  errorType={this.state.errorType}
                  source="home"
                  homePageUrl="vmall://com.vmall.client/home/main?tabIndex=0&from=rn"
                  pageType="refreshPage"
                  errorRefresh={this.errorRefresh}
                />
              )
            );
          return this.props.mineData && this.state.cmsData?.pageInfos?.length
            ? this.renderPage(styles, theme)
            : placeholderContent;
        }}
      </WithTheme>
    );
  }

  renderPage = (styles, theme) => {
    if (PlatformUtils.isApp()) {
      return <GestureHandlerRootView>{this._loadPage(styles, theme)}</GestureHandlerRootView>;
    } else {
      return this._loadPage(styles, theme);
    }
  };

  errorRefresh = () => {
    this.setState({
      error: false,
    });
    this._getPageInfo();
  };

  // 登录状态传递
  _isLogin = () => {
    this.eventListenerLogin = DeviceEventEmitter.addListener('NativeCallAction', async (event) => {
      let param = event?.param;
      this.handleLogin(event, param);
      // 由于存在监听的先后顺序，进入个人中心事件和离开分类事件不分先后被监听到，所以两个判断不能合并
      this.tabFragment(event, param);
    });
  };

  // 快速切换tab会多次触发弹窗,2s内只响应一次切换事件
  _tabChange = _.throttle(
    () => {
      if (this.flag) {
        this.flag = false;
        clearTimeout(this.dialogTimer);
        this.dialogTimer = setTimeout(() => {
          this.isPersonal = true;
          this.getSysConfig();
        }, 100);
      }
    },
    2000,
    { trailing: false },
  );

  // 下拉刷新组件
  _refreshControl = (theme: any) => {
    return PlatformUtils.isIOS() ? (
      <RefreshControl refreshing={this.state.isRefreshing} tintColor={theme.C31.color} onRefresh={this._onRefresh} />
    ) : (
      <LottieRefreshControl
        ref={(ref) => (this.refreshControl = ref)}
        onRefresh={this._onRefresh}
        primaryColor={theme.C32.color}
        darkStyle={this.props.DarkStyle}
        headerHeight={lottieViewHeight}
        // 不展示系统状态栏时需要去掉状态栏高度，当前只有vde产品存在这个场景
        lottieViewHeight={this.props.statusBarHeight <= 0 ? lottieViewHeight - 39 : lottieViewHeight}
        fromWhere={PAGE_TYPE.personal}
      />
    );
  };

  _productTitleAndMore = (e: any) => {
    if (!this.state.productTitleAndMore && this.state.productTitleAndMore !== e) {
      this.setState({
        productTitleAndMore: e,
      });
    }
  };
  isPaddTop = () => {
    return PlatformUtils.isApp() && this.state.userAccount && this.state.isJsLogin;
  };
  _onScroll = (e: any) => {
    const _contentOffsetY = e.nativeEvent.contentOffset.y;
    this.eventOffsetY = _contentOffsetY;
    this.state.scrollY.setValue(_contentOffsetY);
    DeviceEventEmitter.emit('onOutScrollViewScroll', e.nativeEvent.contentOffset.y, PAGE_TYPE.personal);
    // 处理ios端曝光时监听onMomentumScrollEnd事件不准确的问题
    if (PlatformUtils.isIOS() || PlatformUtils.isHarmony()) {
      this.timer && clearTimeout(this.timer);
      this.timer = setTimeout(() => {
        if (PlatformUtils.isHarmony()) {
          const event = {
            nativeEvent: {
              contentOffset: { x: 0, y: this.eventOffsetY },
            },
          };
          DeviceEventEmitter.emit('onScrollEvent', event, PAGE_TYPE.personal);
        } else {
          DeviceEventEmitter.emit('iosForOnScrollEvent', e, PAGE_TYPE.personal);
        }
      }, 1000);
    }
  };

  /**
   * 渲染APP
   * @private
   */
  _renderApp = (styles: any, theme: any, groupStyleChangesProps: any, headStyle: any) => {
    const bottom = this.state.cmsData?.pageInfos?.length && JSON.parse(JSON.stringify(this.state.cmsData.pageInfos[0]));
    if (bottom.cards.length <= 2) {
      return null;
    }
    const cards = [];
    if (bottom.cards && bottom.cards.length) {
      for (let i = 0; i < bottom.cards.length; i++) {
        if (
          bottom.cards[i].cardType === 'prod' &&
          i === bottom.cards.length - 1
        ) {
          cards.push(bottom.cards[i]);
          bottom.cards = cards;
        }
      }
    }
    if (bottom.cards.length > 0) {
      const bottomChildren = jsonConvert(bottom, PAGE_TYPE.personal).children;
      let product;
      for (let i = 0; i < bottomChildren.length; i++) {
        if (bottomChildren[i].type === 'prod') {
          product = bottomChildren[i];
        }
      }
      const header = this._renderAppTop(groupStyleChangesProps, headStyle);
      const props = product.props;
      // 头部
      props.topComponent = header;
      // ref
      props.scrollViewRef = (ref: any) => {
        this.scroller = ref;
      };
      // refreshControl
      props.refreshControl = this._refreshControl(theme);
      props.uniqueKey = PAGE_TYPE.personal;
      // 刷新组件的高度值
      props.heightForRefreshControl = 96;
      // style
      props.pageStyle = styles.commonStyle;
      // onScroll
      props.onScroll = this._onScroll;
      // 页面滚动开始事件
      props.onScrollBeginDrag = this._onScrollBeginDrag;
      // 页面滚动结束事件
      props.onScrollEndDrag = this._onScrollEndDrag;
      // 页面滚动结束事件
      props.onMomentumScrollEnd = this._onMomentumScrollEnd;
      props.isNewWaterfall = true;
      // 回调商品组件的子标题和更多
      props.productTitleAndMore = (e) => this._productTitleAndMore(e);
      props.vproLogoTagHolder = this.otherParams?.vproLogoTagHolder || '';
      props.getVproLogoFinish = this.state.getVproLogoFinish;
      props.recommendFlag = this.state.recommendFlag;
      props.oaid = this.props.oaid || '';
      props.recyclerListOneByTwo = this.recyclerListOneByTwo;
      return <Product {...props} />;
    }
  };

  /**
   * 渲染顶部组件
   * @param headStyle
   * @private
   */
  _renderAppTop = (groupStyleChangesProps: any, headStyle: any) => {
    const top = this.state.cmsData?.pageInfos?.length && JSON.parse(JSON.stringify(this.state.cmsData.pageInfos[0]));
    const vproList =
      this.state.cmsData?.pageInfos?.length && JSON.parse(JSON.stringify(this.state.cmsData.pageInfos[0])).cards[0];
    const cards = [];
    if (top.cards && top.cards.length) {
      for (let i = 0; i < top.cards.length; i++) {
        if (i !== top.cards.length - 1) {
          cards.push(top.cards[i]);
        }
      }
    }
    top.cards = cards;
    const disPlayApk = vproList?.configInfo && JSON.parse(vproList.configInfo).display;
    const isMember = this.getIsMember(disPlayApk);
    return (
      <View
        onLayout={(e: any) => {
          pageHeaderStore.setHeaderHeight(PAGE_TYPE.personal, e.nativeEvent.layout.height);
        }}
      >
        {/* 顶部子页签 */}
        <PersonalHead
          configInfo={this.state.configInfo}
          isLogin={this.state.isJsLogin}
          enableAdvancedFeature={this.enableAdvancedFeature}
          titleOpacity={this.state.titleOpacity}
          cartNum={this.state.cartNum}
          messageNum={this.state.messageNum}
          avaImg={this.state.avaImg}
          userName={this.state.userName}
          userAccount={this.state.userAccount}
          userLevel={this.state.userLevel}
          headStyle={headStyle}
          groupStyleChanges={groupStyleChangesProps}
          pageId={this.state.reportPageId}
          lang={this.props.lang}
          ref={this.refSon}
          vproList={vproList}
          isVpro={this.state.isVpro}
          personalStyleChange={this.personalStyleChange}
          userId={this.userId}
          appPackageName={AppidStore.apkPackageName}
          pageCatName={this.pageCatName}
          statusBarHeight={this.props.statusBarHeight}
        />
        {this.showMarginTop(isMember)}
        <DynamicComponent
          // @ts-expect-error 忽略TS检查
          {...jsonConvert(top, PAGE_TYPE.personal, undefined, false, this.otherParams)}
          mapComponents={MapComponents}
          stickyScrollY={this.state.scrollY}
          key={this.scrollViewKey}
          pageType={PAGE_TYPE.personal}
        />
        {
          // 当存在场景购底部导航时，需要给页面多留24+bottomNavHeight（正常是56，大字体状态下会更高）的高度，防止最底部的组件被遮挡
          this.isDisplayScenePurchaseNavBottom && (
            <View
              style={{
                height: 24 + this.scenePurchaseNavBottomData?.bottomNavHeight,
              }}
            />
          )
        }
        {/* 新版瀑布流时，此处展示瀑布流的子标题 */}
        {/** 商品返回方法回调，不再返回dom, 返回dom导致标题栏无法触发其他场景刷新，会一直使用同一个dom，返回方法可实现刷新效果 */}
        {typeof this.state.productTitleAndMore === 'function' ? this.state.productTitleAndMore('',this.state.recommendFlag) : this.state.productTitleAndMore}
      </View>
    );
  };
  // 点击“开启”跳转native
  clickOpen = () => {
    this.setState({
      isShow: false,
    });
    const params = {
      switchState: {
        system: this.state.system,
        logistics: this.state.logistics,
        service: this.state.service,
        activity: this.state.activity,
        shortMessage: this.state.shortMessage,
      },
      scene: '0', // 0：普通场景， 1：预约场景
      pageURL: '/portal/personal/', // 来源页URL
      type: '2',
    };
    RnBridge.invokeVmallNative('common', 'openNotificationSettings', {
      data: JSON.stringify(params),
    })
      .then(() => {})
      .catch(() => {});
  };

  clickClose = () => {
    const time = new Date().getTime();
    StorageUtil.setSpValueAll('notifyCloseTime', time.toString(), 'String');
    this.setState({
      isShow: false,
    });
  };

  /**
   * 计算页面的渲染时间、网络耗时等，目前通过ref计算比较准确
   */
  calculateCostOnRef = (ref) => {
    if (this.isCaculated || !ref) {
      return;
    }
    this.isCaculated = true;
    this.reportHmiEnd();
  };

  renderLoginComponent = (convertResult: any) => {
    const { screenWidth, screenHeight } = CommonUtils.getWindowSize();
    RecordUtils.info(TAG, `AppStore.isLogin:${AppStore.isLogin}`);
    if (!AppStore.isLogin && convertResult?.loginInfo?.isSoupportLoginComp) {
      return (
        <LoginCompnent
          screenWidth={screenWidth}
          screenHeight={screenHeight}
          loginTip={convertResult?.loginInfo?.loginBtnTxt}
          pageType={PAGE_TYPE.personal}
          pageId={convertResult?.loginInfo?.pageId}
          cardId={convertResult?.loginInfo?.cardId}
          isNeedOffset={this.isDisplayScenePurchaseNavBottom}
          offsetHeight={this.scenePurchaseNavBottomData?.bottomNavHeight}
        />
      );
    }
  };
  getBackTopOffsetHeight = (convertResult: any) => {
    let heigth = 0;
    // 场景购距离底部的高度
    if (this.isDisplayScenePurchaseNavBottom) {
      heigth = this.scenePurchaseNavBottomData?.bottomNavHeight - 56;
    }
    // 登录组件展示时 置顶按钮的高度偏移  -- 由于场景购计算的是偏移量，再次累加组件时需要计算组件的高度
    if (this.isDisplayScenePurchaseNavBottom && !AppStore.isLogin && convertResult?.loginInfo?.isSoupportLoginComp) {
      heigth = heigth + 26 + CommonUtils.getScaleSize(18, FONT_MUTIPLE.FONT_LEVEL_SIX);
    }
    // 与活动页不动，活动页的置顶按钮距离底部为68 首页和个人中心的距离为48
    return (
      heigth +
      (!AppStore.isLogin && convertResult?.loginInfo?.isSoupportLoginComp
        ? CommonUtils.getScaleSize(12, FONT_MUTIPLE.FONT_LEVEL_SIX)
        : 0)
    );
  };
  getIsShowLogin(convertResult: any) {
    const { isSoupportLoginComp } = convertResult?.loginInfo || {};
    return !AppStore.isLogin && isSoupportLoginComp;
  }
  getBackTopOffsetHeightHarmony = (convertResult: any) => {
    // 底部操作区域高度
    let heigth = 0;
    const isShowLogin = this.getIsShowLogin(convertResult);
    // 场景购存在时,底部操作区域高度
    if (this.isDisplayScenePurchaseNavBottom) {
      heigth = this.scenePurchaseNavBottomData?.bottomNavHeight;
      // 场景购+登录组件时底部操作区域高度
      if (isShowLogin) {
        heigth = heigth + 28 + CommonUtils.getScaleSize(18, FONT_MUTIPLE.FONT_LEVEL_SIX) + 8;
      }
    } else if (isShowLogin) {
      heigth = 28 + CommonUtils.getScaleSize(18, FONT_MUTIPLE.FONT_LEVEL_SIX) + 20;
    }
    return heigth;
  };
  hasCacheControl = (timeSpace) => {
    return timeSpace < this.remainDays ? false : true;
  };

  // 通知弹窗是否展示
  isShowNotifyDialogFunc = async (isShowNotify = false, result: any) => {
    await HttpService.querySystemConfig(`['RN_MESSAGE_NOTIFY_DONOT_DISTURB_DAYS']`).then((res) => {
      if (res.systemConfigInfos) {
        this.remainDays = Number(res.systemConfigInfos.RN_MESSAGE_NOTIFY_DONOT_DISTURB_DAYS?.systemConfigValue) || 30;
      }
    });
    const lastTime = (await StorageUtil.getSpValueAll('notifyCloseTime', 'String')) || 0;
    const today = new Date().getTime();
    const minusTime = Number(today) - Number(lastTime);
    const timeSpace = minusTime / (24 * 60 * 60 * 1000);
    const isLogin = AppStore.isLogin;
    const cacheControl = this.hasCacheControl(timeSpace);
    const isYoung = CONSUME_YEAR_TYPE.includes(this.consumeYear);
    const consumeYear = !isYoung;
    const sysNotifyJusge = isShowNotify;
    return cacheControl && isLogin && consumeYear && sysNotifyJusge;
  };

  // 弹窗展示信息获取
  getNotifyInfo = () => {
    RnBridge.invokeVmallNative('common', 'getNotificationSwitch').then(async (result: any) => {
      if (result) {
        if (this.getNotificationSwitchStatus(result)) {
          const isShowNotifyDialog = await this.isShowNotifyDialogFunc(true, result);
          this.setState({
            system: result.system,
            logistics: result.logistics,
            service: result.service,
            activity: result.activity,
            shortMessage: result.shortMessage,
            isShowNotifyDialog: isShowNotifyDialog,
            isShow: true,
          });
        } else {
          this.setState({
            isShowNotifyDialog: false,
            isShow: false,
          });
        }
      } else {
        this.setState({
          isShowNotifyDialog: false,
          isShow: false,
        });
      }
    });
  };

  // 检查native返回的开关状态
  getNotificationSwitchStatus = (params: any) => {
    return (
      params.system === '0' ||
      params.logistics === '0' ||
      params.service === '0' ||
      params.activity === '0' ||
      params.shortMessage === '0'
    );
  };

  // 消息开关提醒浮层
  renderNotifyComponent = () => {
    const { screenWidth, screenHeight } = CommonUtils.getWindowSize();
    const { isShow, isShowNotifyDialog, sysNoticeShow } = this.state;
    if (isShow && isShowNotifyDialog && String(sysNoticeShow) === '1') {
      return (
        <NotifyCompnent
          screenWidth={screenWidth}
          screenHeight={screenHeight}
          clickOpen={this.clickOpen}
          clickClose={this.clickClose}
          sysNoticeBtnTxt={this.state.sysNoticeBtnTxt}
          sysNoticeTxt={this.state.sysNoticeTxt}
          isNeedOffset={this.isDisplayScenePurchaseNavBottom}
          offsetHeight={this.scenePurchaseNavBottomData?.bottomNavHeight}
          pageType={PAGE_TYPE.personal}
          pageId={this.state.reportPageId}
        />
      );
    }
  };

  private tabFragment(event: any, param: any) {
    if (event?.action === 'tabCurrent' && event?.service === 'tabFragment') {
      this.handleTabFragment(param, event);
    }
  }

  private handleTabFragment(param: any, event: any) {
    if (param?.userVisibleHint && this.state.isJsLogin) {
      // 登录后切换调取固定区域接口
      this._tabChange();
    } else if (this.state.isJsLogin) {
      this.isJsLogin(event);
    } else if (Number(param?.currentIndex) === 4 && !param.isCurrentIndex && this.isPersonal) {
      this.flag = true;
      this.isPersonal = false;
      clearTimeout(this.dialogTimer);
    }
  }

  private isJsLogin(event: any) {
    if (
      Number(event?.param?.currentIndex) === 4 &&
      (event.param.isCurrentIndex === true || event.param.isCurrentIndex === 'true')
    ) {
      this.updateSonRef();
      // 刷新用户名
      this._queryUserInfo();
    }
  }

  private handleLogin(event: any, param: any) {
    if (event?.service === 'login' && event?.action === 'loginOut') {
      const isJsLogin = param?.isLogin ? true : false;
      AppStore.isLogin !== isJsLogin && AppStore.setIsLogin(isJsLogin);
      RecordUtils.info(TAG, `isJsLogin:${isJsLogin}`);
      if (this.state.isJsLogin === isJsLogin) {
        return;
      }
      this.setState({
        isJsLogin,
      });
      if (param.isLogin) {
        this.getRecommendFlagTimer && clearTimeout(this.getRecommendFlagTimer);
        this.getRecommendFlagTimer = setTimeout(() => {
          this.getRecommendFlag(param.isLogin);
        }, 500);
        // 获取apk传递值，有值取值，没值调接口
        this.setState(
          {
            avaImg: event.param.headPictureURL,
            userName: event.param.nickName,
          },
          () => {
            this._queryUserInfo(event.param.headPictureURL, event.param.nickName);
            this.updateSonRef();
          },
        );
        this.isPersonal = true;
        Number(param?.tabindex) === 4 && this.getSysConfig();
      } else {
        this.setState({
          avaImg: '',
          userName: '',
          isVpro: '',
          userLevel: '',
          userAccount: '',
        });
        this.isPersonal = false;
        this.otherParams.userInfo = null;
        // 清空会员信息
        LoginStore.setIsLogin(false);
        LoginStore.setUserName('');
        LoginStore.setUserLevel('');
        LoginStore.setExperience(0);
        LoginStore.setNextExperience(0);
        LoginStore.setAvaImg('');
        this.setStatusBarStyle();
        this.consumeYear = '1';
      }
    }
  }

  private renderBirthDayGift(styles) {
    return this.state.dialogType && this.state.isJsLogin ? (
      <BirthdayGift
        styles={styles}
        type={this.state.dialogType}
        content={this.state.templateContent}
        point={this.giftPoint}
        env={env}
        caculteDate={this.caculteDate.bind(this)}
        changeDialog={this.changeDialog.bind(this)}
      />
    ) : null;
  }

  private handleRenderApp(jsonCards: any) {
    if (this.props.transparentExtraInfo && typeof this.props.transparentExtraInfo === 'string') {
      const extraProps = JSON.parse(this.props.transparentExtraInfo);
      const openRecycler = 'is_open_recyclerlist';
      // 默认打开, 只有配置为0的时候才关闭
      this.recyclerListOneByTwo =
        PlatformUtils.isAndroid() &&
        !(extraProps?.[openRecycler] === '0') &&
        jsonCards[jsonCards.length - 1]?.layout.layoutType === 'TwoColumnLayout';
    }
    return (
      (jsonCards &&
        jsonCards.length > 0 &&
        jsonCards[jsonCards.length - 1]?.cardType === 'prod' &&
        (jsonCards[jsonCards.length - 1]?.layout.layoutType === 'StaggeredLayout' || this.recyclerListOneByTwo))
    );
  }

  private onScroll() {
    return Animated.event(
      [
        {
          nativeEvent: { contentOffset: { y: this.state.scrollY } }, // 记录滑动距离
        },
      ],
      {
        useNativeDriver: false,
        listener: (e: any) => {
          this.eventOffsetY = e.nativeEvent.contentOffset.y;
          DeviceEventEmitter.emit('onOutScrollViewScroll', e.nativeEvent.contentOffset.y, PAGE_TYPE.personal);
          if (PlatformUtils.isIOS() || PlatformUtils.isHarmony()) {
            this.timer && clearTimeout(this.timer);
            this.timer = setTimeout(() => {
              if (PlatformUtils.isHarmony()) {
                const event = {
                  nativeEvent: {
                    contentOffset: { x: 0, y: this.eventOffsetY },
                  },
                };
                DeviceEventEmitter.emit('onScrollEvent', event, PAGE_TYPE.personal);
              } else {
                DeviceEventEmitter.emit('iosForOnScrollEvent', e, PAGE_TYPE.personal);
              }
              // 触发滚动结束
            }, 1000);
          }
        },
      }, // 使用原生动画驱动
    );
  }

  private handleDisplayScenePurchaseNavBottom() {
    // 当存在场景购底部导航时，需要给页面多留24+bottomNavHeight（正常是56，大字体状态下会更高）的高度，防止最底部的组件被遮挡
    const { width, height } = this.props;
    let viewHeight = this.isDisplayScenePurchaseNavBottom ? this.scenePurchaseNavBottomData?.bottomNavHeight : 0;
    if (PlatformUtils.isHarmony() && ScreenUtils.isPadHorizontal(width, height)) {
      viewHeight = viewHeight + 24;
    }
    return (
      <View
        style={{
          height: viewHeight,
        }}
      />
    );
  }

  private handleScenePurchaseNavBottom(convertResult) {
    if (convertResult?.scenePurchaseNavBottom?.isDisplay) {
      this.isDisplayScenePurchaseNavBottom = true;
      this.scenePurchaseNavBottomData = convertResult?.scenePurchaseNavBottom?.scenePurchaseNavBottomData;
    }
  }

  private getIsMember(disPlayApk: any) {
    return (
      String(this.props.enableAdvancedFeature) !== '0' &&
      this.state.isJsLogin &&
      this.state.isVpro === '1' &&
      String(disPlayApk) === '1'
    );
  }

  private showScenePurchaseNavBottom() {
    return (
      this.isDisplayScenePurchaseNavBottom && (
        <ScenePurchaseBottomNavLayout scenePurchaseBottomNavData={this.scenePurchaseNavBottomData} />
      )
    );
  }

  private showDynamicComponent(pageInfos: any) {
    return (
      <DynamicComponent
        // @ts-expect-error 忽略TS检查
        {...jsonConvert(pageInfos, PAGE_TYPE.personal, undefined, false, this.otherParams)}
        mapComponents={MapComponents}
        stickyScrollY={this.state.scrollY}
        key={this.scrollViewKey}
      />
    );
  }

  private showMarginTop(isMemberShow: any) {
    return (
      <View
        style={{
          marginTop: isMemberShow ? 12 : 0,
          alignItems: 'center',
        }}
      />
    );
  }

  private showFixedButton(styles: any, pageInfos: any) {
    return (
      <View pointerEvents="box-none" style={styles.boxNone}>
        {/* 浮标 */}
        <FixedButton
          {...jsonConvert(pageInfos, PAGE_TYPE.personal)}
          fixedButton={false}
          pageType={PAGE_TYPE.personal}
          pageId={this.state.reportPageId}
          pageCatCode={this.pageCatCode}
          pageCatName={this.pageCatName}
        />
      </View>
    );
  }

  private renderPersonalTitle(
    isMember: boolean,
    headStyle: any,
    styleChange: any,
    size: string,
    pageType: any,
    vproList: any,
  ) {
    const { width, statusBarHeight } = this.props;
    return (
      <View
        style={{
          position: 'absolute',
          top: -2,
          left: 0,
          elevation: 2,
          zIndex: 1,
          width,
          opacity: this.navOpacityAnimated,
          height: PlatformUtils.isIOS() ? 56 : 56 + statusBarHeight,
        }}
        pointerEvents={Number(this.navOpacityAnimated) === 0 ? 'none' : 'auto'}
      >
        <PersonalTitle
          width={width}
          isMember={isMember}
          configInfo={this.state.configInfo}
          isLogin={this.state.isJsLogin}
          enableAdvancedFeature={this.enableAdvancedFeature}
          isShow={true}
          avaImg={this.state.avaImg}
          userName={this.state.userName}
          userAccount={this.state.userAccount}
          userLevel={this.state.userLevel}
          cartNum={this.state.cartNum}
          messageNum={this.state.messageNum}
          headStyle={headStyle}
          pageId={this.state.reportPageId}
          mergeStyle={
            !CommonUtils.isEmpty(styleChange) ? CommonUtils.getChangeStyle(styleChange, size, pageType) : null
          }
          vproList={vproList}
          appPackageName={AppidStore.apkPackageName}
          statusBarHeight={statusBarHeight}
        />
      </View>
    );
  }

  _loadPage = (styles: any, theme: any) => {
    const { pageType, width, lang, statusBarHeight } = this.props;
    const {
      cmsData,
      isJsLogin,
      recommendFlag,
      isVpro,
      titleOpacity,
      cartNum,
      messageNum,
      configInfo,
      avaImg,
      userName,
      userAccount,
      userLevel,
      reportPageId,
    } = this.state;
    const jsonCards =
      cmsData?.pageInfos?.length && JSON.parse(JSON.stringify(cmsData.pageInfos[0])).cards;
    // 标题栏变装
    const headStyle = this.headStyle;
    const groupStyleChangesProps = this.groupStyleChanges;
    const styleChange = this.personalStyleChange;
    // 屏幕尺寸类型
    const size = getScreenSize(width);
    const vproList =
      cmsData?.pageInfos?.length && JSON.parse(JSON.stringify(cmsData.pageInfos[0])).cards[0];
    const disPlayApk = vproList?.configInfo && JSON.parse(vproList?.configInfo)?.display;
    const isMember = this.getIsMember(disPlayApk);
    this.otherParams.isLogin = isJsLogin;
    this.otherParams.isGroupFlag = this.isGroupFlag;
    this.otherParams.recommendFlag = recommendFlag;
    this.otherParams.isVpro = isVpro;
    const pageInfos = cmsData?.pageInfos?.length && cmsData.pageInfos[0];
    const convertResult = jsonConvert(pageInfos, PAGE_TYPE.personal, undefined, false, this.otherParams);
    this.handleScenePurchaseNavBottom(convertResult);
    return (
      <View onLayout={this._onLayout} style={{ marginBottom: PlatformUtils.isIOS() ? iosBottomBarHeight : 0 }}>
        <View style={styles.personalBody} ref={this.calculateCostOnRef}>
          {this.renderPersonalTitle(isMember, headStyle, styleChange, size, pageType, vproList)}
          {/* 下面是页面主体部分，包括顶部子页签和子页签下面所有内容 */}
          {this.handleRenderApp(jsonCards) ? (
            this._renderApp(styles, theme, groupStyleChangesProps, headStyle)
          ) : (
            <Animated.ScrollView
              ref={(ref: any) => {
                this.scroller = ref;
              }}
              refreshControl={this._refreshControl(theme)}
              style={styles.commonStyle}
              onScroll={this.onScroll()}
              scrollEventThrottle={1}
              showsVerticalScrollIndicator={false}
              showsHorizontalScrollIndicator={false}
              overScrollMode={PlatformUtils.isHarmony() ? 'always' : 'never'}
              // 页面滚动开始事件
              onScrollBeginDrag={this._onScrollBeginDrag}
              // 页面滚动结束后事件
              onScrollEndDrag={this._onScrollEndDrag}
              onMomentumScrollEnd={this._onMomentumScrollEnd}
              removeClippedSubviews={true}
            >
              {/* 顶部子页签 */}
              <PersonalHead
                isLogin={isJsLogin}
                enableAdvancedFeature={this.enableAdvancedFeature}
                titleOpacity={titleOpacity}
                cartNum={cartNum}
                messageNum={messageNum}
                configInfo={configInfo}
                avaImg={avaImg}
                userName={userName}
                userAccount={userAccount}
                userLevel={userLevel}
                groupStyleChanges={groupStyleChangesProps}
                headStyle={headStyle}
                pageId={reportPageId}
                lang={lang}
                ref={this.refSon}
                vproList={vproList}
                isVpro={isVpro}
                personalStyleChange={styleChange}
                userId={this.userId}
                statusBarHeight={statusBarHeight}
              />
              {this.showMarginTop(isMember)}
              {this.showDynamicComponent(pageInfos)}
              {this.handleDisplayScenePurchaseNavBottom()}
            </Animated.ScrollView>
          )}
          {/* 下面是页面浮标 */}
          {this.showFixedButton(styles, pageInfos)}
          {/* 右下角回到顶部按钮 */}
          <FixedButton
            {...jsonConvert(pageInfos, PAGE_TYPE.personal)}
            fixedButton={true}
            onBackTop={this.onBackTop}
            pageType={PAGE_TYPE.personal}
            pageId={reportPageId}
            pageCatCode={this.pageCatCode}
            pageCatName={this.pageCatName}
            needInnerStyle={true}
            bottomNavHeight={
              PlatformUtils.isHarmony()
                ? this.getBackTopOffsetHeightHarmony(convertResult)
                : this.getBackTopOffsetHeight(convertResult)
            }
          />
          {/* 弹窗 */}
          <Toast pageType={PAGE_TYPE.personal} />
        </View>
        {this.renderBirthDayGift(styles)}
        {this.showScenePurchaseNavBottom()}
        {this.renderLoginComponent(convertResult)}
        {this.renderNotifyComponent()}
       </View>
    );
  };
}
export default Personal;
