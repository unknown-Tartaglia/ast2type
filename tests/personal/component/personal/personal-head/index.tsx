/*
 *@Date: 2022-01-05 10:20:11
 *@Description: 个人中心吸顶状态头部
 */
import {
  CommonUtils,
  componentautoscaling,
  Cookies,
  PlatformUtils,
  screenSize as getScreenSize,
  t,
  WithTheme,
  RouterUtils,
  itemExposeHoc,
  monitor,
  EventTracking,
  Service as env,
  URL_CONSTANTS,
  ScreenUtils,
  INTERNAL_JUMP_LINK,
  PAGE_TYPE,
} from '@hw-vmall/vrn-basic-comp';
import React, { Component } from 'react';
import { Dimensions, View, DeviceEventEmitter, Animated } from 'react-native';
import ImgArray from '../../../../../assets/ImgArray';
import IconList from '../../../../../component/basic1/title/components/IconList/index';
import dapReportList from './dapReportList';
import styles from './style/index';
import AnimationHeader from './animation/';
const LOGINANDREG_NAME = 'logInAndReg';
class PersonalTitle extends Component<any, any> {
  logInAndRegList: any = null;
  hasLogInAndRegIcon: boolean = false;
  scrollEmitter: any = null;
  titleAnimatedValue = new Animated.Value(1);
  userInfoAnimatedValue = new Animated.Value(0);
  isShowTitle: boolean = true;
  constructor(props) {
    super(props);
    this.state = {
      pageType: this.props.pageType || 'personal',
      iconList: [{}],
      canClick: true,
    };
  }
  componentDidMount() {
    this.scrollEmitter = DeviceEventEmitter.addListener(
      'onOutScrollViewScroll',
      (contentOffset: number, pageType: string) => {
        if (pageType !== PAGE_TYPE.personal) {
          return;
        }
        if (contentOffset > 40 && this.isShowTitle) {
          this.isShowTitle = false;
          Animated.timing(this.titleAnimatedValue, {
            toValue: 0,
            duration: 80,
            useNativeDriver: true,
          }).start(() => {
            Animated.timing(this.userInfoAnimatedValue, {
              toValue: this.isShowTitle ? 0 : 1,
              duration: 340,
              useNativeDriver: true,
            }).start();
          });
          this.setState({ canClick: this.isShowTitle });
        }
        if (contentOffset <= 40 && !this.isShowTitle) {
          this.isShowTitle = true;
          Animated.timing(this.userInfoAnimatedValue, {
            toValue: 0,
            duration: 340,
            useNativeDriver: true,
          }).start(() => {
            Animated.timing(this.titleAnimatedValue, {
              toValue: !this.isShowTitle ? 0 : 1,
              duration: 80,
              useNativeDriver: true,
            }).start();
          });
          this.setState({ canClick: this.isShowTitle });
        }
      },
    );
    const { headStyle } = this.props;
    headStyle && headStyle.iconTexts && headStyle.iconTexts.length !== 0
      ? this.handleIconList(headStyle.iconTexts)
      : null;
  }

  componentWillUnmount() {
    this.scrollEmitter && this.scrollEmitter.remove();
  }

  /**
   * 处理所有标题数据
   * 返回数据源编号集合
   * @param list 标题icon数据源
   */
  handleIconList(list: Array<any>) {
    const ICON_NAME = PlatformUtils.isIOS()
      ? ['personalCenter', 'message', 'homePage', 'search', 'setting', 'userContentCenter', 'custom']
      : ['scan', 'cart', 'personalCenter', 'message', 'homePage', 'search', 'setting', 'userContentCenter', 'custom'];
    const iconList = list.map((item, index) => {
      const isCart = item.iconAttribute === 'cart';
      const isMessage = item.iconAttribute === 'message';
      return {
        iconUrl: item.iconAttribute === 'custom' ? env.cmsCndProdPath + item.imgUrl : item.iconAttribute + 'Show',
        iconText: this.handleIconText(item.iconAttribute, item.title),
        actionUrl: this.handleIconUrl(item.iconAttribute, item),
        iconNo: item.iconAttribute === LOGINANDREG_NAME && list.length !== 1 ? list.length + 1 : index + 1,
        gotoPageId: index + 1,
        clickType: this.handleListType(item.iconAttribute),
        isCart,
        isMessage,
        listName: item.iconAttribute,
      };
    });
    const relList = iconList.filter((list) => {
      return ICON_NAME.includes(list.listName);
    });
    this.setState({
      iconList: relList.length > 10 ? relList.slice(0, 10) : relList,
    });
    // 判断是否包含登录和注册Icon
    this.hasLogInAndRegIcon = list.some((item) => {
      return PlatformUtils.isWap(Dimensions.get('window').width) && item.iconAttribute === LOGINANDREG_NAME;
    });
    this.logInAndRegList = iconList.filter((item) => {
      return LOGINANDREG_NAME.includes(item.listName);
    });
  }
  handleIconText(text: string, title: any): any {
    switch (text) {
      case 'homePage':
        // 首页
        return title || t('tab_index');
      case 'scan':
        // 扫一扫
        return title || t('scan');
      case 'cart':
        // 购物车
        return title || t('shortcut_cart');
      case 'personalCenter':
        // 我的
        return title || t('service');
      case 'message':
        // 消息中心
        return title || t('message_center');
      case 'search':
        // 搜索
        return title || t('search');
      case 'setting':
        // 设置
        return title || t('setting');
      case 'userContentCenter':
        // 用户内容中心
        return title || t('userContentCenter');
      case 'logInAndReg':
        // 登录和注册
        return title || t('login');
      case 'custom':
        // 自定义
        return title;
      default:
        break;
    }
  }

  handleApkUrl(url: string, iconUrl: any) {
    const targetRoute = 'SearchDefault';
    let configInfo = {
      searchHotListShow: 'true', // 热搜榜是否显示
      searchResultPageProdShow: 'true', // 结果页商品是否显示
      searchHistoryShow: 'true', // 历史记录是否显示
      searchResultPageActivityShow: 'true', // 结果活动是否显示
      searchResultPageContentShow: 'true', // 结果页内容是否显示
    };
    if (this.props.configInfo) {
      configInfo = JSON.parse(this.props.configInfo) || {};
    }
    const apkUrl = `vmall://com.vmall.client/home/rnSearch?targetRoute=${targetRoute}&searchHistoryShow=${configInfo.searchHistoryShow}&searchHotListShow=${configInfo.searchHotListShow}&searchResultPageProdShow=${configInfo.searchResultPageProdShow}&searchResultPageActivityShow=${configInfo.searchResultPageActivityShow}&searchResultPageContentShow=${configInfo.searchResultPageContentShow}`;
    switch (url) {
      case 'homePage':
        return iconUrl || INTERNAL_JUMP_LINK.APP_HOMEPAGEURL;
      case 'scan':
        return iconUrl || INTERNAL_JUMP_LINK.APP_SCAN_URL;
      case 'cart':
        return iconUrl || INTERNAL_JUMP_LINK.APP_CART_URL;
      case 'personalCenter':
        return iconUrl || INTERNAL_JUMP_LINK.APP_PERSONCENTER_URL;
      case 'message':
        return iconUrl || INTERNAL_JUMP_LINK.APP_MESSAGEURL;
      case 'search':
        return iconUrl || PlatformUtils.isIOS() ? 'vmall://com.vmall.client/home/search' : apkUrl;
      case 'setting':
        return iconUrl || INTERNAL_JUMP_LINK.APP_SETTINGURL;
      case 'userContentCenter':
        return iconUrl || INTERNAL_JUMP_LINK.APP_USERCONTENTCENTER_URL;
      case 'custom':
        return iconUrl;
      default:
        break;
    }
  }

  handleIconUrl(url: string, item: any): any {
    return PlatformUtils.isApp() ? this.handleApkUrl(url, item.actionUrl) : this.handleWapUrl(url, item.actionUrlWap);
  }

  handleWapUrl(url: string, iconUrl: any) {
    const targetRoute = 'SearchDefault';
    let configInfo = {
      searchHistoryShow: 'true', // 历史记录是否显示
      searchHotListShow: 'true', // 热搜榜是否显示
      searchResultPageProdShow: 'true', // 结果页商品是否显示
      searchResultPageActivityShow: 'true', // 结果活动是否显示
      searchResultPageContentShow: 'true', // 结果页内容是否显示
      searchFindShow: 'true',
      prodSearchScope: 'all',
      relativeWordShow: 'true',
      searchScence: '',
    };
    if (this.props.configInfo) {
      configInfo = JSON.parse(this.props.configInfo) || {};
    }
    let wapSearchUrl = `${env.wapDomain}portal/search/index.html?targetRoute=${targetRoute}&searchHistoryShow=${configInfo.searchHistoryShow}&searchHotListShow=${configInfo.searchHotListShow}&searchResultPageProdShow=${configInfo.searchResultPageProdShow}&searchResultPageActivityShow=${configInfo.searchResultPageActivityShow}&searchResultPageContentShow=${configInfo.searchResultPageContentShow}`;
    if (!!configInfo.searchFindShow) {
      wapSearchUrl = `${wapSearchUrl}&searchFindShow=${configInfo.searchFindShow}&relativeWordShow=${configInfo.relativeWordShow}&prodSearchScope=${configInfo.prodSearchScope}&searchScence=${configInfo.searchScence}`;
    }
    switch (url) {
      case 'scan':
        return iconUrl || INTERNAL_JUMP_LINK.APP_SCAN_URL;
      case 'cart':
        return iconUrl || `${env.wapDomain}cart`;
      case 'personalCenter': {
        let rnPersonalUrl = env.wapDomain + URL_CONSTANTS.PERSONAL_URL_WAP;
        if (Cookies.get('rnpersonalurlwap')) {
          rnPersonalUrl = Cookies.get('rnpersonalurlwap');
        } else {
          rnPersonalUrl = env.wapDomain + URL_CONSTANTS.PERSONAL_URL_WAP;
        }
        return iconUrl || rnPersonalUrl;
      }
      case 'message':
        return iconUrl || `${env.wapDomain}message/index`;
      case 'homePage':
        return iconUrl || `${env.wapDomain}`;
      case 'search':
        return iconUrl || wapSearchUrl;
      case 'setting':
        return iconUrl || `${env.wapDomain}setting/index`;
      case 'userContentCenter':
        return iconUrl || `${env.wapDomain}content/index`;
      case 'logInAndReg':
        return iconUrl;
      case 'custom':
        return iconUrl;
      default:
        break;
    }
  }
  handleListType(type: string): any {
    switch (type) {
      case 'message':
        return '10';
      case 'homePage':
        return '22';
      case 'scan':
        return '28';
      case 'cart':
        return '21';
      case 'personalCenter':
        return '23';
      case 'search':
        return '20';
      case 'setting':
        return '9';
      case 'userContentCenter':
        return '24';
      case 'custom':
        return '25';
      default:
        break;
    }
  }
  isApp = () => {
    return this.getSize() === 'small';
  };
  isPc = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return PlatformUtils.isPc(width);
  };
  getSize = () => {
    return getScreenSize(this.props.width);
  };
  // 屏幕尺寸大于1200，并为web平台下，渲染为pad样式
  isPadPc = () => {
    return this.getSize() === 'medium' && this.isPadHorizonta() && this.props.width >= 1024;
  };
  isPad = () => {
    return this.getSize() === 'medium';
  };
  isPadHorizonta = () => {
    const sWidth = PlatformUtils.isWeb()
      ? Dimensions.get('window').width
      : CommonUtils.getWindowSize('personal').screenWidth;
    const sHeight = PlatformUtils.isWeb()
      ? Dimensions.get('window').height
      : CommonUtils.getWindowSize('personal').screenHeight;
    return sWidth >= sHeight;
  };
  loginWeb(actionName) {
    const path: string = encodeURIComponent(window.location.href);
    const loginUrl = this.isPc()
      ? `${env.webDomain}account/login?url=${path}`
      : `${env.wapDomain}account/applogin?url=${path}`;
    this.props.clickItem(this.isPc() ? 310000101 : 210000101, loginUrl, actionName?.includes('昵称') ? 2 : 1);
    EventTracking.execReportData('', true);
    RouterUtils.gotoPage(loginUrl, false);
  }
  goLogin = () => {
    this.loginWeb('昵称');
  };
  userInfoClick = (actionName?: any) => {
    const url = this.isPc()
      ? `${env.upUserUrl}`
      : `${env.wapDomain}portal/activity/index.html?pn=MemberPrivilegeWAP&isShowLayout=false
          `;

    if (this.props.isLogin) {
      this.props.clickItem(this.isPc() ? 310000101 : 210000101, url, actionName?.includes('昵称') ? 2 : 1);
      EventTracking.execReportData('', true);
      RouterUtils.gotoPage(url);
    } else {
      // 未登录情况下拉起登录
      this.loginWeb(actionName);
    }
  };

  getWidth = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    const height: number = CommonUtils.getWindowSize('personal').screenHeight;
    return { width, height };
  };

  sourceResult = (newMergeStyle) => {
    const { imgStyle, bgImg } = newMergeStyle || {};
    if (this.isPc()) {
      return ImgArray.headeBgpc;
    } else {
      if (!newMergeStyle || (!bgImg && !imgStyle.backgroundColor) || this.props.isMember) {
        return this.getHeadImg();
      } else if (newMergeStyle) {
        if (imgStyle?.backgroundColor === 'transparent' && bgImg) {
          return bgImg;
        }
      }
    }
  };
  private getHeadImg() {
    if (this.props.isMember) {
      if (ScreenUtils.isMedium(this.getWidth().width)) {
        return ScreenUtils.isPadHorizontal(this.getWidth().width, this.getWidth().height)
          ? ImgArray.upBgPad
          : ImgArray.upBgPadS;
      }
      return ImgArray.upBg;
    } else {
      if (ScreenUtils.isMedium(this.getWidth().width)) {
        return ScreenUtils.isPadHorizontal(this.getWidth().width, this.getWidth().height)
          ? ImgArray.headBgPad
          : ImgArray.headBgPadS;
      }
      return ImgArray.headBg;
    }
  }

  // 个人中心只展示消息和扫一扫图标，暂时展示设置
  getIconList = () => {
    const { iconList } = this.state;
    const arr: any = [];
    if (iconList?.length > 0) {
      iconList.map((item: any) => {
        const clickType = Number(item.clickType);
        if (clickType === 28 || clickType === 9 || clickType === 10) {
          arr.push(item);
        }
      });
      arr.sort((a, b) => Number(a.iconNo) - Number(b.iconNo));
    }
    return arr;
  };

  private initVariable(vproList: any, newMergeStyle: any) {
    const item = vproList?.configInfo && JSON.parse(vproList.configInfo);
    const showText = item?.showAvatarSetting === '1' && item.avatar !== '';
    const showIcon = item?.showAvatarSetting === '2' && item.avatarIcon !== '';
    const avatarIcon = item?.avatarIcon;
    const imgBgUri = this.props.isMember ? null : newMergeStyle?.bgImg;
    let memberStyle = newMergeStyle?.imgStyle?.backgroundColor ? newMergeStyle.imgStyle : {};
    memberStyle = this.props.isMember ? {} : memberStyle;
    return { showText, item, showIcon, avatarIcon, imgBgUri, memberStyle };
  }

  private getMarginLeft(showText: any, marginLeft: number, showIcon: any) {
    if (showText) {
      marginLeft = -5;
    } else if (showIcon) {
      marginLeft = -3;
    }
    return marginLeft;
  }

  renderShowHeader = (
    memberStyle,
    _styles,
    newMergeStyle,
    isLogin,
    showText,
    item,
    showIcon,
    avatarIcon,
    marginLeft,
    mergeStyle,
    unLoginText,
    iconList,
    defaultAvatar,
  ) => {
    const { userName, userLevel, isMember } = this.props;
    return (
      <View
        style={[_styles.animationView, memberStyle, newMergeStyle?.imgStyle, { width: this.getWidth().width }]}
      >
        <View style={[_styles.avartWrap]}>
          <AnimationHeader
            _styles={_styles}
            mergeStyle={mergeStyle}
            unLoginText={unLoginText}
            newMergeStyle={unLoginText}
            isLogin={isLogin}
            showText={showText}
            item={item}
            showIcon={showIcon}
            avatarIcon={avatarIcon}
            marginLeft={marginLeft}
            defaultAvatar={defaultAvatar}
            userInfoAnimatedValue={this.userInfoAnimatedValue}
            titleAnimatedValue={this.titleAnimatedValue}
            userInfoClick={this.userInfoClick}
            canClick={this.state.canClick}
            goLogin={this.goLogin}
            userName={userName}
            userLevel={userLevel}
            isMember={isMember}
            avaImg={this.props.avaImg}
          />
        </View>
        <View style={_styles.iconList}>
          {iconList.length > 0 && (
            <IconList
              style={_styles}
              size={this.getSize()}
              fromPage={'personal'}
              cartNum={this.props.cartNum}
              messageNum={this.props.messageNum}
              pageId={this.props.pageId}
              iconList={this.state.iconList}
              mergeStyle={mergeStyle}
              newMergeStyle={newMergeStyle}
              pageCatName={t('personal')}
              pageCatCode={'p_personalCenter'}
              resSiteCode={'s_personalCenter_head'}
              resSiteName={t('top_card')}
              hasLogInAndRegIcon={this.hasLogInAndRegIcon}
              logInAndRegList={this.logInAndRegList}
              isTitleLogin={this.props.isLogin}
              avaImg={this.props.avaImg}
            />
          )}
        </View>
      </View>
    );
  };

  render() {
    const { isLogin, mergeStyle, vproList, isMember } = this.props;
    const newMergeStyle = mergeStyle;
    const { showText, item, showIcon, avatarIcon, memberStyle } = this.initVariable(vproList, newMergeStyle);
    let marginLeft = 0;
    marginLeft = this.getMarginLeft(showText, marginLeft, showIcon);
    const unLoginText = PlatformUtils.isHarmony() ? t('harmonyLogin') : `${t('login')}/${t('register')}`;
    const defaultAvatar = ImgArray.icAvatar;
    return (
      <WithTheme themeStyles={(theme) => styles(theme, this.isPad(), this.props.titleOpacity, newMergeStyle, isMember)}>
        {(_styles, theme) => {
          const { changeColor } = this.props;
          // 图标变装颜色
          let mergeStyle = this.getMergeStyle(newMergeStyle, isMember, theme);
          if (changeColor?.textStyle?.color && !isMember) {
            mergeStyle = changeColor.textStyle.color;
          }
          let newMergeImgStyle = newMergeStyle?.imgStyle?.backgroundColor ? newMergeStyle?.imgStyle : {};
          newMergeImgStyle = isMember ? {} : newMergeImgStyle;
          const iconList = this.getIconList();
          return (
            <>
              {this.renderShowHeader(
                memberStyle,
                _styles,
                newMergeStyle,
                isLogin,
                showText,
                item,
                showIcon,
                avatarIcon,
                marginLeft,
                mergeStyle,
                unLoginText,
                iconList,
                defaultAvatar,
              )}
            </>
          );
        }}
      </WithTheme>
    );
  }

  private getMergeStyle(newMergeStyle: any, isMember: any, theme) {
    const color = theme.C11.color;
    return {
      textStyle: {
        color: newMergeStyle?.textStyle?.color && !isMember ? newMergeStyle.textStyle.color : color,
      },
    };
  }
}
export default componentautoscaling(monitor(dapReportList)(itemExposeHoc(PersonalTitle)));
